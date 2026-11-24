-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qs_ext_inj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T09:44:35.041415+00:00
-- url     : https://prove2.me/submissions/92446119-a7ec-420d-bfd6-31c2b3f3f8ca

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QsRemIffAdd
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QsSymDMatEq
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QsColHHigh
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qs_ext_mem

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.ColumnFamilies
variable {n : ℕ} [NeZero n]
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution (mu : Fin n → ℤ) : Function.Injective (qs_ext mu) := by
  intro I I' h
  funext c
  apply Subtype.ext
  rw [← qs_ext_mem, ← qs_ext_mem, h]
end Formalism.InvariantFactorPaths.ColumnFamilies
