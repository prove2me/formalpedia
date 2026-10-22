-- Prove2me | solution 1 for BirkhoffGlobalSection.positive_clock_inverse_derivative
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-10-03T22:26:18.807432+00:00
-- url     : https://prove2.me/submissions/e5aa7195-0926-406e-9528-1f41c3a444df

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

theorem solution (clock : ℝ ≃o ℝ) (r : ℝ → ℝ)
    (hd : ∀ t, HasDerivAt clock (r t) t) (hpos : ∀ t, 0 < r t) (t : ℝ) :
    HasDerivAt clock.symm (r (clock.symm t))⁻¹ t := by
  exact (hd (clock.symm t)).of_local_left_inverse clock.symm.continuous.continuousAt
    (hpos (clock.symm t)).ne' (Filter.Eventually.of_forall clock.apply_symm_apply)
