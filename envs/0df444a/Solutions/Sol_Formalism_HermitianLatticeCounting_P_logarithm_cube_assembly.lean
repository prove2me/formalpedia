-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.logarithm_cube_assembly
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:58:10.222488+00:00
-- url     : https://prove2.me/submissions/21d96f1e-3229-47bf-b546-5fb77e1ebd1f

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
theorem _root_.solution : MassBoundOfFactorBounds := by
  intro f h2 I hE d hd hI hhE h hIb hEb
  have hL : 0 ≤ Real.log d := Real.log_nonneg hd
  set L := 1 + Real.log d with hLdef
  have hL1 : 0 ≤ L := by positivity
  have hd0 : 0 ≤ d := by linarith
  calc h2 ≤ I * ((2 : ℝ) ^ f * hE) ^ 2 * d ^ 2 := h
    _ ≤ (d * L ^ f) * ((2 : ℝ) ^ f * (d * L ^ (2 * f))) ^ 2 * d ^ 2 := by gcongr
    _ = (4 : ℝ) ^ f * d ^ 5 * L ^ (5 * f) := by
        have : (4 : ℝ) ^ f = (2 ^ f) ^ 2 := by rw [← pow_mul, mul_comm, pow_mul]; norm_num
        rw [this]; ring
end Formalism.HermitianLatticeCounting.P
