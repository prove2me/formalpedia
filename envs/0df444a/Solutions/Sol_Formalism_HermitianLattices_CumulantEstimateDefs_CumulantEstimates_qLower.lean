-- Prove2me | solution 1 for Formalism.HermitianLattices.CumulantEstimateDefs.CumulantEstimates.qLower
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:11:44.745372+00:00
-- url     : https://prove2.me/submissions/4958eacf-44d3-4f43-b481-a2ba698b3cb6

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
theorem _root_.solution : Formalism.HermitianLattices.CumulantEstimateDefs.QuadraticFormLowerBound := by
  unfold Formalism.HermitianLattices.CumulantEstimateDefs.QuadraticFormLowerBound
  intro N lam sg X h₀ hX hz hgap
  rw [halfSum N sg (fun a b => ‖X a b‖ ^ 2) (fun a b => normSymm N X hX a b)
    (fun a b h => by simp [hz a b h])]
  rw [show ∀ S : ℝ, h₀ * (2 * S) / 2 = h₀ * S from fun S => by ring, Finset.mul_sum]
  refine Finset.sum_le_sum fun a _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_le_sum fun b hb => ?_
  obtain ⟨hlt, hne⟩ := (Finset.mem_filter.1 hb).2
  have h1 := hgap a b hlt hne
  have h2 : ((b : ℕ) : ℝ) < ((a : ℕ) : ℝ) := by exact_mod_cast hlt
  exact mul_le_mul_of_nonneg_right (by linarith) (by positivity)
end Formalism.HermitianLattices.CumulantEstimateDefs.CumulantEstimates
