-- Prove2me | solution 1 for Formalism.L2.Th1.D.TraceDualSums.sum_zmod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-1
-- created : 2026-11-24T21:47:20.010843+00:00
-- url     : https://prove2.me/submissions/309ffe73-c0a9-4eaa-b2ec-d449a1aa43ff

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_BiextensionHypothesesOfLevelOne
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_StatementK
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_GaussSumParity_KummerThetaLogarithms_TraceDualExists

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.D
open Formalism.InvariantFactorPaths.G7 (UnrOK)
open Formalism.L2.Th1.D.TraceDualSums
namespace Formalism.L2.Th1.D.TraceDualSums
theorem _root_.solution {M : Type} [AddCommMonoid M] (d : ℕ) [NeZero d] (F : ℕ → M) :
    (∑ s : ZMod d, F s.val) = ∑ i ∈ Finset.range d, F i := by
  cases d with
  | zero => exact absurd rfl (NeZero.ne 0)
  | succ n =>
    rw [Finset.sum_range]
    rfl
end Formalism.L2.Th1.D.TraceDualSums
