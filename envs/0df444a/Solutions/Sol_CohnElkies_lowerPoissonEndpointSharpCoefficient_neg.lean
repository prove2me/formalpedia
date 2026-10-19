-- Prove2me | solution 1 for CohnElkies.lowerPoissonEndpointSharpCoefficient_neg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:25.301796+00:00
-- url     : https://prove2.me/submissions/eb7a6825-8005-4826-aaf4-034b4c6bb578

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_lowerPoissonEndpointSharpCoefficient_eq

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Interval Topology
namespace CohnElkies
theorem _root_.solution
    {c : ℝ} (hc : 0 < c)
    (hsharp : c < Real.pi⁻¹) :
    Real.log (2 * Real.pi * Real.exp 1 * c ^ 2) +
      limitingPoissonEndpointExpectation < 0 := by
  rw [lowerPoissonEndpointSharpCoefficient_eq hc]
  have hproduct : Real.pi * c < 1 := by
    have hdiv : c < 1 / Real.pi := by
      simpa [one_div] using! hsharp
    have h := (lt_div_iff₀ Real.pi_pos).mp hdiv
    nlinarith
  have hpositive : 0 < Real.pi * c :=
    mul_pos Real.pi_pos hc
  have hbelow : Real.pi ^ 2 * c ^ 2 < 1 := by
    have hfactor :
        0 < (1 - Real.pi * c) *
          (1 + Real.pi * c) :=
      mul_pos (sub_pos.mpr hproduct) (by linarith)
    nlinarith
  exact Real.log_neg (by positivity) hbelow
end CohnElkies
