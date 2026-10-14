-- Prove2me | solution 1 for DbarRegularity.norm_iteratedFDeriv_fderiv_apply_le
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-13T15:08:18.336605+00:00
-- url     : https://prove2.me/submissions/ecce0ed9-846d-4bd2-a60b-60f7e30a2bcc

import Definitions.Def_DbarRegularity_Setting
import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.ContDiff.Bounds
import Mathlib.Analysis.Calculus.ContDiff.Comp
import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.FDeriv.CompCLM
import Mathlib.Analysis.Normed.Operator.NormedSpace
import Mathlib.Analysis.Complex.OperatorNorm
import Mathlib.Analysis.Complex.Basic



namespace DbarRegularity

open scoped ContDiff

/-- The `j`-th derivative of a directional derivative `x ↦ Dg(x) w` is bounded by `‖w‖` times the
`(j+1)`-st derivative of `g`. -/
theorem norm_iteratedFDeriv_fderiv_apply_le {D F : Type*} [NormedAddCommGroup D]
    [NormedSpace ℝ D] [NormedAddCommGroup F] [NormedSpace ℝ F] {g : D → F} (j : ℕ)
    (hg : ContDiff ℝ (j + 1) g) (w z : D) :
    ‖iteratedFDeriv ℝ j (fun x => fderiv ℝ g x w) z‖
      ≤ ‖w‖ * ‖iteratedFDeriv ℝ (j + 1) g z‖ := by
  have hfd : ContDiff ℝ j (fderiv ℝ g) := hg.fderiv_right le_rfl
  have hL : ‖ContinuousLinearMap.apply ℝ F w‖ ≤ ‖w‖ :=
    ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg w)
      (fun L => by simpa [mul_comm] using L.le_opNorm w)
  have h := (ContinuousLinearMap.apply ℝ F w).norm_iteratedFDeriv_comp_left
    (n := j) (x := z) hfd.contDiffAt le_rfl
  rw [← norm_iteratedFDeriv_fderiv (x := z)]
  calc ‖iteratedFDeriv ℝ j (fun x => fderiv ℝ g x w) z‖
      = ‖iteratedFDeriv ℝ j ((ContinuousLinearMap.apply ℝ F w) ∘ fderiv ℝ g) z‖ := rfl
    _ ≤ ‖ContinuousLinearMap.apply ℝ F w‖ * ‖iteratedFDeriv ℝ j (fderiv ℝ g) z‖ := h
    _ ≤ ‖w‖ * ‖iteratedFDeriv ℝ j (fderiv ℝ g) z‖ := by gcongr

end DbarRegularity

open DbarRegularity

open scoped ContDiff

theorem solution {D F : Type*} [NormedAddCommGroup D]
    [NormedSpace ℝ D] [NormedAddCommGroup F] [NormedSpace ℝ F] {g : D → F} (j : ℕ)
    (hg : ContDiff ℝ (j + 1) g) (w z : D) :
    ‖iteratedFDeriv ℝ j (fun x => fderiv ℝ g x w) z‖
      ≤ ‖w‖ * ‖iteratedFDeriv ℝ (j + 1) g z‖ :=
  norm_iteratedFDeriv_fderiv_apply_le j hg w z
