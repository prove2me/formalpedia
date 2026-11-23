-- Prove2me | solution 1 for Formalism.HermitianLattices.GL2PrimeSums.TailSumsHookFormulaTorsion.log_step
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:27:32.678815+00:00
-- url     : https://prove2.me/submissions/2b88e156-99fd-4284-9a81-eae9d9775ac1

import Mathlib
import Definitions.Def_Formalism_GL3MeanSquares_SmoothedRemainderRealIntegralFormula
import Definitions.Def_Formalism_GL3MeanSquares_HookFormulaTorsion_ExpNegLeDivPowFour

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Finset Filter Topology
open Formalism Formalism.HermitianLattices Formalism.HermitianLattices.GL2PrimeSums Formalism.HermitianLattices.GL2PrimeSums.TailSumsHookFormulaTorsion
namespace Formalism.HermitianLattices.GL2PrimeSums.TailSumsHookFormulaTorsion
theorem _root_.solution (n : ℕ) (hn : 1 ≤ n) :
    1 / (((n + 1 : ℕ) : ℝ)) ≤ Real.log ((n + 1 : ℕ) : ℝ) - Real.log (n : ℝ) := by
  have hn' : (0 : ℝ) < n := by exact_mod_cast hn
  have hn1 : (0 : ℝ) < ((n + 1 : ℕ) : ℝ) := by positivity
  have h := Real.log_le_sub_one_of_pos (div_pos hn' hn1)
  rw [Real.log_div hn'.ne' hn1.ne'] at h
  have e : (n : ℝ) / ((n + 1 : ℕ) : ℝ) - 1 = - (1 / ((n + 1 : ℕ) : ℝ)) := by
    push_cast
    field_simp
    ring
  rw [e] at h
  linarith
end Formalism.HermitianLattices.GL2PrimeSums.TailSumsHookFormulaTorsion
