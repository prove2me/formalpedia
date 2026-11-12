-- Prove2me | solution 1 for AvramDividend.Classical.avram_a06_zero_grid_conditional_fourier_20261111
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T19:47:48.039844+00:00
-- url     : https://prove2.me/submissions/68c480bb-d442-467e-8207-121591262218

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Finset
noncomputable section

/-- The empty Fourier grid contributes the constant unit factor. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (N : Fin 1 → Ω → ℕ) (Y : ℕ → Ω → ℝ) :
    ∀ t : WithLp 2 (Fin 0 → ℝ), ∃ φ : Fin 0 → ℕ → ℂ,
      MeasureTheory.charFun
        (Measure.map (fun ω : Ω => WithLp.toLp 2 (fun i : Fin 0 =>
          ∑ j ∈ Finset.Ico (N i.castSucc ω) (N i.succ ω), Y j ω)) P) t =
        ∫ ω, ∏ i : Fin 0, φ i (N i.succ ω - N i.castSucc ω) ∂P
      ∧ ∀ i : Fin 0, MeasureTheory.charFun
          (Measure.map (fun ω : Ω =>
            ∑ j ∈ Finset.Ico (N i.castSucc ω) (N i.succ ω), Y j ω) P)
          (t.ofLp i) =
          ∫ ω, φ i (N i.succ ω - N i.castSucc ω) ∂P := by
  intro t
  refine ⟨fun i => i.elim0, ?_, ?_⟩
  · have hConst :
        (fun ω : Ω => WithLp.toLp 2 (fun i : Fin 0 =>
          ∑ j ∈ Finset.Ico (N i.castSucc ω) (N i.succ ω), Y j ω)) =
          (fun _ : Ω => (0 : WithLp 2 (Fin 0 → ℝ))) := by
      funext ω
      ext i
      exact i.elim0
    simp [hConst, MeasureTheory.charFun_dirac]
  · intro i
    exact i.elim0
