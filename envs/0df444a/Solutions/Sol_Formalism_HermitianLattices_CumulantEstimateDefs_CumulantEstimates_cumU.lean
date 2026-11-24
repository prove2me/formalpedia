-- Prove2me | solution 1 for Formalism.HermitianLattices.CumulantEstimateDefs.CumulantEstimates.cumU
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T07:04:42.006255+00:00
-- url     : https://prove2.me/submissions/2a2f9e08-4d19-4f1f-ae84-e7ef621286f9

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_QuadraticFormLowerBound
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_HilbertSchmidtHalfBound

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.CumulantEstimateDefs Formalism.HermitianLattices.CumulantEstimateDefs.CumulantEstimates
open Finset
namespace Formalism.HermitianLattices.CumulantEstimateDefs.CumulantEstimates
theorem _root_.solution : CumulantUpperBound := by
  unfold CumulantUpperBound
  intro ι _ P y hP hsum hmean hy
  have hpos : 0 < ∑ j, P j * Real.exp (y j) := by
    have h1 : ∑ j, P j * Real.exp (-1) ≤ ∑ j, P j * Real.exp (y j) :=
      Finset.sum_le_sum fun j _ =>
        mul_le_mul_of_nonneg_left (Real.exp_le_exp.2 (by linarith [(abs_le.1 (hy j)).1])) (hP j)
    rw [← Finset.sum_mul, hsum, one_mul] at h1
    linarith [Real.exp_pos (-1)]
  have hle : ∑ j, P j * Real.exp (y j) ≤ ∑ j, P j * (1 + y j + y j ^ 2) :=
    Finset.sum_le_sum fun j _ => by
      have h2 := Real.abs_exp_sub_one_sub_id_le (hy j)
      exact mul_le_mul_of_nonneg_left (by linarith [(abs_le.1 h2).2]) (hP j)
  have hexp : ∑ j, P j * (1 + y j + y j ^ 2) = ∑ j, P j + ∑ j, P j * y j + ∑ j, P j * y j ^ 2 := by
    rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => by ring
  have hlog := Real.log_le_sub_one_of_pos hpos
  linarith
end Formalism.HermitianLattices.CumulantEstimateDefs.CumulantEstimates
