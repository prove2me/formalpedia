-- Prove2me | solution 1 for CohnElkies.tendsto_lowerPoissonEndpointSharpCoefficient
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:25.301796+00:00
-- url     : https://prove2.me/submissions/5a0b789c-8367-4274-bc09-a08d771e7ae1

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_tendsto_lowerPoissonEndpointExpectation
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
    {c : ℝ} (hc : 0 < c) :
    Tendsto
      (fun σ : ℝ =>
        Real.log (2 * Real.pi * Real.exp 1 * c ^ 2) +
          lowerPoissonEndpointExpectation σ)
      (𝓝[<] 1)
      (𝓝 (Real.log (Real.pi ^ 2 * c ^ 2))) := by
  rw [← lowerPoissonEndpointSharpCoefficient_eq hc]
  exact tendsto_const_nhds.add
    tendsto_lowerPoissonEndpointExpectation
end CohnElkies
