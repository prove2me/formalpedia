-- Prove2me | solution 1 for BianchiIX.hasDerivAt_clock_projected_variation
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T23:28:04.102741+00:00
-- url     : https://prove2.me/submissions/8c1ad01d-8d4f-4450-b53c-def28bfb2a27

import Mathlib.Analysis.Calculus.FDeriv.Symmetric
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Tactic.NormNum
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Tactic.Module


namespace BianchiIX
end BianchiIX

noncomputable section
open BianchiIX
open Filter
open scoped Topology
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]


/-- Removing the clock displacement leaves only the state derivative at fixed clock. -/
theorem solution
    {field : ℝ × E → E} {J : (ℝ × E) →L[ℝ] E}
    {theta dtheta : ℝ → ℝ} {Y dY : ℝ → E} {a b t : ℝ}
    (hfield : HasFDerivAt field J (theta t, Y t))
    (htheta : HasDerivAt theta a t)
    (hY : HasDerivAt Y (a • field (theta t, Y t)) t)
    (hdtheta : HasDerivAt dtheta b t)
    (hdY : HasDerivAt dY
      (b • field (theta t, Y t) + a • J (dtheta t, dY t)) t) :
    HasDerivAt (fun s => dY s - dtheta s • field (theta s, Y s))
      (a • J (0, dY t - dtheta t • field (theta t, Y t))) t := by
  have hF := hfield.comp_hasDerivAt t (htheta.prodMk hY)
  have hJa : J (a, a • field (theta t, Y t)) = a • J (1, field (theta t, Y t)) := by
    rw [← map_smul]
    congr 1
    simp
  have hJ : J (0, dY t - dtheta t • field (theta t, Y t)) =
      J (dtheta t, dY t) - dtheta t • J (1, field (theta t, Y t)) := by
    rw [← map_smul, ← map_sub]
    congr 1
    ext <;> simp
  apply (hdY.sub (hdtheta.smul hF)).congr_deriv
  rw [hJa, hJ]
  simp only [Function.comp_apply]
  module
