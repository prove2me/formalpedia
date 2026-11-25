-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.convex_body_condition
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-25T17:02:22.144145+00:00
-- url     : https://prove2.me/submissions/2472b821-09f9-4bf0-af9b-253b6fea094d

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
theorem _root_.solution : ConvexBodyCond := by
  intro f rd hrd
  have h1 : (2 : ℝ) ^ (4 * f) * ((2 : ℝ) ^ (2 * f))⁻¹ * (rd ^ f) ^ 2 = (4 * rd ^ 2) ^ f := by
    rw [pow_mul, pow_mul, ← inv_pow, ← mul_pow, ← pow_mul, mul_comm f 2, pow_mul, ← mul_pow]
    norm_num
  rw [h1]
  apply pow_le_pow_left₀ (by positivity)
  have := Real.pi_gt_three
  have h9 : (9 : ℝ) ≤ Real.pi ^ 2 := by nlinarith
  nlinarith [sq_nonneg rd]
end Formalism.HermitianLatticeCounting.P
