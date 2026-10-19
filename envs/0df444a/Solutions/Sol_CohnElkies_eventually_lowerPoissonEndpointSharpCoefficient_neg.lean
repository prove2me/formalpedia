-- Prove2me | solution 1 for CohnElkies.eventually_lowerPoissonEndpointSharpCoefficient_neg
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:25.301796+00:00
-- url     : https://prove2.me/submissions/447df9ca-7375-489e-bed7-4ba1dfd38856

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_lowerPoissonEndpointSharpCoefficient_eq
import Theorems.Thm_CohnElkies_lowerPoissonEndpointSharpCoefficient_neg
import Theorems.Thm_CohnElkies_tendsto_lowerPoissonEndpointSharpCoefficient

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
    ∀ᶠ σ : ℝ in 𝓝[<] 1,
      Real.log (2 * Real.pi * Real.exp 1 * c ^ 2) +
        lowerPoissonEndpointExpectation σ < 0 := by
  have hlimit := tendsto_lowerPoissonEndpointSharpCoefficient hc
  have hnegative : Real.log (Real.pi ^ 2 * c ^ 2) < 0 := by
    rw [← lowerPoissonEndpointSharpCoefficient_eq hc]
    exact lowerPoissonEndpointSharpCoefficient_neg hc hsharp
  exact hlimit (Iio_mem_nhds hnegative)
end CohnElkies
