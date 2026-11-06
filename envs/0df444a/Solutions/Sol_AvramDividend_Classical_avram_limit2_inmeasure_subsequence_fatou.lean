-- Prove2me | solution 1 for AvramDividend.Classical.avram_limit2_inmeasure_subsequence_fatou
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T23:16:45.83678+00:00
-- url     : https://prove2.me/submissions/c49c00fd-6f6d-4d03-bc2d-15efda48cb0d

import Mathlib.MeasureTheory.Function.ConvergenceInMeasure
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter
open scoped ENNReal
noncomputable section

/-- Physical stopped meshes converging in probability have an almost-sure
    subsequence satisfying the extended-real Fatou payoff lower bound. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (F : ℕ → Ω → ℝ) (R : Ω → ℝ)
    (hMeasure : TendstoInMeasure P F atTop R) :
    ∃ ns : ℕ → ℕ,
      StrictMono ns ∧
      (∀ᵐ ω ∂P, ENNReal.ofReal (R ω) ≤
        liminf (fun n => ENNReal.ofReal (F (ns n) ω)) atTop) := by
  obtain ⟨ns, hmono, hAE⟩ := hMeasure.exists_seq_tendsto_ae
  refine ⟨ns, hmono, ?_⟩
  filter_upwards [hAE] with ω hω
  have hENN : Tendsto (fun n => ENNReal.ofReal (F (ns n) ω)) atTop
      (nhds (ENNReal.ofReal (R ω))) :=
    (ENNReal.continuous_ofReal.tendsto _).comp hω
  rw [hENN.liminf_eq]
