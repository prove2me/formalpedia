-- Prove2me | solution 1 for AvramDividend.Classical.avram_a06_single_grid_constant_fourier_factor_20261111
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T19:47:43.362392+00:00
-- url     : https://prove2.me/submissions/5a571d51-1743-4cd4-91ec-36af516011f2

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Finset
noncomputable section

/-- A one-coordinate Fourier grid needs only a constant Fourier factor. -/
theorem solution
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P]
    (D : Ω → ℕ) (Z : Ω → ℝ) (hZ : Measurable Z)
    (t : WithLp 2 (Fin 1 → ℝ)) :
    ∃ φ : Fin 1 → ℕ → ℂ,
      MeasureTheory.charFun
        (Measure.map (fun ω : Ω => WithLp.toLp 2 (fun _ : Fin 1 => Z ω)) P) t =
          ∫ ω, ∏ i : Fin 1, φ i (D ω) ∂P
      ∧ ∀ i : Fin 1, MeasureTheory.charFun (Measure.map Z P) (t.ofLp i) =
          ∫ ω, φ i (D ω) ∂P := by
  refine ⟨fun i _ => MeasureTheory.charFun (Measure.map Z P) (t.ofLp i), ?_, ?_⟩
  · have hInd : iIndepFun (fun _ : Fin 1 => Z) P :=
      ProbabilityTheory.iIndepFun.of_subsingleton
    have hChar :=
      (ProbabilityTheory.iIndepFun_iff_charFun_pi
        (fun _ : Fin 1 => hZ.aemeasurable)).mp hInd t
    rw [hChar]
    simp
  · intro i
    simp
