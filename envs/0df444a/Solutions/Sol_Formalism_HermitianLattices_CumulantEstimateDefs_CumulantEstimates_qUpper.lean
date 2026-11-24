-- Prove2me | solution 1 for Formalism.HermitianLattices.CumulantEstimateDefs.CumulantEstimates.qUpper
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:11:45.161376+00:00
-- url     : https://prove2.me/submissions/122dd1b3-6ff7-4d27-a4a9-9ec076aed41d

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_QuadraticFormLowerBound
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_HilbertSchmidtHalfBound
import Theorems.Thm_Formalism_HermitianLattices_CumulantEstimateDefs_CumulantEstimates_halfSum
import Theorems.Thm_Formalism_HermitianLattices_CumulantEstimateDefs_CumulantEstimates_normSymm

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.CumulantEstimateDefs Formalism.HermitianLattices.CumulantEstimateDefs.CumulantEstimates
open Finset MeasureTheory
open scoped ComplexOrder
namespace Formalism.HermitianLattices.CumulantEstimateDefs.CumulantEstimates
theorem _root_.solution : Formalism.HermitianLattices.CumulantEstimateDefs.QuadraticFormUpperBound := by
  unfold Formalism.HermitianLattices.CumulantEstimateDefs.QuadraticFormUpperBound
  intro N lam sg X lamAbs hX hz hbd
  rw [halfSum N sg (fun a b => ‖X a b‖ ^ 2) (fun a b => normSymm N X hX a b)
    (fun a b h => by simp [hz a b h])]
  rw [show ∀ S : ℝ, (lamAbs + N) * (2 * S) / 2 = (lamAbs + N) * S from fun S => by ring,
    Finset.mul_sum]
  refine Finset.sum_le_sum fun a _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun b _ => ?_
  have h1 := le_trans (le_abs_self (lam b - lam a)) (hbd b a)
  have h2 : ((a : ℕ) : ℝ) < N := by exact_mod_cast a.isLt
  have h3 : (0 : ℝ) ≤ ((b : ℕ) : ℝ) := Nat.cast_nonneg _
  exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
end Formalism.HermitianLattices.CumulantEstimateDefs.CumulantEstimates
