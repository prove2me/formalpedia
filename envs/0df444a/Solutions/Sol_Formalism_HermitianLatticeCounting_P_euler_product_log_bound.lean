-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.euler_product_log_bound
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:10:58.675803+00:00
-- url     : https://prove2.me/submissions/fc22743a-04f2-4361-ba8a-df4f1be565ff

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
theorem _root_.solution : EulerLog := by
  intro ι s e X h0 h1 he
  have hL : 0 ≤ -Real.log (1 - X) := by
    have : Real.log (1 - X) ≤ 0 := Real.log_nonpos (by linarith) (by linarith)
    linarith
  push_cast
  rw [Finset.sum_mul]
  apply Finset.sum_le_sum
  intro p hp
  have hpow : X ^ e p ≤ X := by
    calc X ^ e p ≤ X ^ 1 := pow_le_pow_of_le_one h0.le h1.le (he p hp)
      _ = X := pow_one X
  have h2 : Real.log (1 - X) ≤ Real.log (1 - X ^ e p) := Real.log_le_log (by linarith) (by linarith)
  have h3 : (1 : ℝ) ≤ e p := by exact_mod_cast he p hp
  nlinarith
end Formalism.HermitianLatticeCounting.P
