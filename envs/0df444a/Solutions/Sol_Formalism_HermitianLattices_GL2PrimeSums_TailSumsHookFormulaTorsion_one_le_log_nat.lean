-- Prove2me | solution 1 for Formalism.HermitianLattices.GL2PrimeSums.TailSumsHookFormulaTorsion.one_le_log_nat
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:27:32.914398+00:00
-- url     : https://prove2.me/submissions/d9264374-e0b4-4239-b128-358cf6ed5e16

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
theorem _root_.solution (n : ℕ) (hn : 3 ≤ n) : 1 ≤ Real.log (n : ℝ) := by
  have h3 : (3 : ℝ) ≤ n := by exact_mod_cast hn
  rw [Real.le_log_iff_exp_le (by linarith)]
  have := Real.exp_one_lt_three
  linarith
end Formalism.HermitianLattices.GL2PrimeSums.TailSumsHookFormulaTorsion
