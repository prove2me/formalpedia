-- Prove2me | solution 1 for Formalism.HermitianLattices.TraceIntegrality.am_gm_sum_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:53:45.828383+00:00
-- url     : https://prove2.me/submissions/9060aa50-b2ce-4b61-bf0b-892c3e17c0e6

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_ConcavityEquidistribution
import Definitions.Def_Formalism_LogVandermondeBounds_LogVandermondeProofs_GammaIntegralPolynomialBound
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_OrthogonalMinorBound
import Theorems.Thm_Formalism_LogVandermondeBounds_flipTwoThree_amgm_period_lattice_bound


-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.TraceIntegrality
open Finset Matrix
open scoped ComplexOrder
namespace Formalism.HermitianLattices.TraceIntegrality
theorem _root_.solution : AmGmSumLowerBound := by
  intro f v x hf hv hx hprod
  have h := Formalism.LogVandermondeBounds.flipTwoThree.amgm_period_lattice_bound f (2 * v ^ 2) x hf (by positivity) hx
    (by
      have e : (2 * (2 * v ^ 2)) ^ f = (2 * v) ^ (2 * f) := by
        rw [pow_mul]; congr 1; ring
      rw [e]; exact hprod)
  have e : (f : ℝ) / (2 * v) ^ 2 = ((f : ℝ) / (2 * v ^ 2)) / 2 := by
    field_simp
  rw [e]
  linarith
end Formalism.HermitianLattices.TraceIntegrality
