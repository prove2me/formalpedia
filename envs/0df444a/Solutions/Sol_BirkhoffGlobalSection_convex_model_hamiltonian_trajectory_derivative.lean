-- Prove2me | solution 1 for BirkhoffGlobalSection.convex_model_hamiltonian_trajectory_derivative
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-03T22:39:25.992546+00:00
-- url     : https://prove2.me/submissions/05b3d8e8-c5f8-4e69-b245-66909a0097a0

import Theorems.Thm_BirkhoffGlobalSection_convex_model_boundary_contact_positive
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.Order.IntermediateValue
import Mathlib.Topology.Order.Compact
import Mathlib.Order.Hom.Set
import Mathlib.Analysis.Calculus.Deriv.Inverse
import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.Analysis.Calculus.MeanValue
import Theorems.Thm_BirkhoffGlobalSection_hamiltonian_radial_characteristic_normalization

open Set
open scoped Topology ContDiff



set_option autoImplicit false
set_option maxHeartbeats 800000

theorem solution {μ c : ℝ}
    (M : BirkhoffGlobalSection.ConvexRegularizationModel μ c)
    {φ : Flow ℝ (BirkhoffGlobalSection.LeftEnergyState μ c)}
    (D : BirkhoffGlobalSection.ConvexModelDynamics M φ)
    (s : BirkhoffGlobalSection.ConvexModelState M) (t : ℝ) :
    HasDerivAt (fun v => (D.flow v s : BirkhoffGlobalSection.Phase))
      (BirkhoffGlobalSection.hamiltonianVectorField M.modelHamiltonian (D.flow t s)) t := by
  have h := (D.hamiltonian (D.flow t s)).scomp_of_eq t
    ((hasDerivAt_id t).sub_const t) (by simp)
  have h' := h.congr_of_eventuallyEq
    (f₁ := fun v : ℝ => (D.flow v s : BirkhoffGlobalSection.Phase))
    (Filter.Eventually.of_forall (fun v => by
      simp only [Function.comp_apply, id, ← D.flow.map_add, sub_add_cancel]))
  simpa only [one_smul] using h'
