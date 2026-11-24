-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qb_bM_coe
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:35:58.516785+00:00
-- url     : https://prove2.me/submissions/f02afb66-0a18-4f35-ad01-cb3a07991e8c

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_MemSpanStandardIffProjZero
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_FiltrationMaximalQuotient

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Finset Module
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.ColumnFamilies
variable {n : ℕ} [NeZero n]
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution (hA : LemmaA) {M : GLMod n} (CF : ColFam M) (mu : Fin n → ℤ) (j : {j : CF.J // CF.mu j = mu}) :
    ((qb_bM hA CF mu j : ↥(CF.MM mu)) : M.ι → ℤ) = CF.vec j.1 (canT (CF.mu j.1)) := by
  simp [qb_bM]
end Formalism.InvariantFactorPaths.ColumnFamilies
