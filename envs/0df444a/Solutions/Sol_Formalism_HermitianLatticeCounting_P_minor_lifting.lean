-- Prove2me | solution 1 for Formalism.HermitianLatticeCounting.P.minor_lifting
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T16:58:48.700796+00:00
-- url     : https://prove2.me/submissions/d21682fd-1c06-4895-94dc-1b1bf6263d89

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
theorem _root_.solution : MinorLift := by
  intro R _ r Z c hc
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [Matrix.det_updateRow_add, Matrix.updateRow_eq_self, Matrix.vecMul_eq_sum,
      Matrix.det_updateRow_sum, hc]; simp
  · congr 1; ext i j
    simp [Matrix.updateRow_apply, Fin.castSucc_ne_last]
  · rw [Matrix.det_updateCol_add, Matrix.updateCol_eq_self]
    have : Matrix.mulVec Z c = fun k => ∑ i, c i • Z k i := by
      ext k; simp [Matrix.mulVec, dotProduct, mul_comm]
    rw [this, Matrix.det_updateCol_sum, hc]; simp
  · congr 1; ext i j
    simp [Matrix.updateCol_apply, Fin.castSucc_ne_last]
end Formalism.HermitianLatticeCounting.P
