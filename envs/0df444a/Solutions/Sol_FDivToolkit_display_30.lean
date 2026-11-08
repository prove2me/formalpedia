-- Prove2me | solution 1 for FDivToolkit.display_30
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T14:45:35.451393+00:00
-- url     : https://prove2.me/submissions/162ef825-6e9b-4ead-ab03-73f10d37004f

import Definitions.Def_FDivToolkit_IsAdmissibleH
import Definitions.Def_FDivToolkit_Fh

open FDivToolkit in
theorem solution {H : ℝ → ℝ} (hH : IsAdmissibleH H) (y : ℝ) (hy : 1 < y) :
    Fh H y ≤ (y - 1) * H (Real.log y) ∧ (y - 1) * H (Real.log y) ≤ y * H (Real.log y) := by
  have hpos : 0 ≤ H (Real.log y) := by
    rw [← hH.map_zero]
    exact hH.strictMono.monotone (Real.log_nonneg hy.le)
  refine ⟨?_, by nlinarith⟩
  unfold Fh
  have hcont : ContinuousOn (fun z => H (Real.log z)) (Set.uIcc 1 y) := by
    refine hH.continuous.comp_continuousOn (Real.continuousOn_log.mono ?_)
    intro z hz
    rw [Set.uIcc_of_le hy.le] at hz
    simp only [Set.mem_compl_iff, Set.mem_singleton_iff]
    linarith [hz.1]
  calc ∫ z in (1 : ℝ)..y, H (Real.log z) ≤ ∫ z in (1 : ℝ)..y, H (Real.log y) := by
        refine intervalIntegral.integral_mono_on hy.le hcont.intervalIntegrable
          intervalIntegrable_const ?_
        intro z hz
        exact hH.strictMono.monotone (Real.log_le_log (by linarith [hz.1]) hz.2)
    _ = (y - 1) * H (Real.log y) := by
        rw [intervalIntegral.integral_const, smul_eq_mul]
