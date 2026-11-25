-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.logarithm_cube_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:58:17.236423+00:00
-- url     : https://prove2.me/submissions/9b7d1741-19e3-49bc-bbfb-3996b06107dc

import Mathlib
import Definitions.Def_Formalism_FlagUnipotentLattices_LatticeDeterminantIndexSq
import Definitions.Def_Formalism_FlagUnipotentLattices_SignaturePreservingEntryNorms
import Definitions.Def_Formalism_FlagUnipotentLattices_MinkowskiFactorialBounds_IntegerGroupLocalParametrization

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField nonZeroDivisors Finset
noncomputable section
open Formalism Formalism.HermitianLatticeCounting Formalism.HermitianLatticeCounting.P
open Formalism.HermitianLatticeCounting.LocalIntegralStructure Formalism.HermitianLatticeCounting.P.IntegralityLocalGlobal
set_option linter.all false
namespace Formalism.HermitianLatticeCounting.P
theorem _root_.solution : LogMassBound := by
  intro f rd hf hrd
  have hf' : (1 : ℝ) ≤ f := by exact_mod_cast hf
  have hl : 0 ≤ Real.log rd := Real.log_nonneg hrd
  have hrd0 : 0 < rd := by linarith
  have hlog : Real.log (rd ^ f) = f * Real.log rd := Real.log_pow _ _
  have hA : 0 < 1 + Real.log (rd ^ f) := by rw [hlog]; positivity
  rw [Real.log_mul (by positivity) (by positivity), Real.log_mul (by positivity) (by positivity),
    Real.log_pow, Real.log_pow, hlog, Real.log_pow]
  have h4 : Real.log 4 ≤ 2 := by
    have : (4 : ℝ) = 2 ^ 2 := by norm_num
    rw [this, Real.log_pow]
    have := Real.log_two_lt_d9
    push_cast; linarith
  have h5 : Real.log (1 + f * Real.log rd) ≤ Real.log f + Real.log rd := by
    rw [← Real.log_mul (by positivity) (by positivity)]
    apply Real.log_le_log (by positivity)
    have := Real.log_le_sub_one_of_pos hrd0
    nlinarith
  push_cast
  nlinarith
end Formalism.HermitianLatticeCounting.P
