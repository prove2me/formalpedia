-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.standardBasis_coe
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T12:36:00.437628+00:00
-- url     : https://prove2.me/submissions/896e99df-4878-47df-97b1-91190acb42df

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
theorem _root_.solution (hS : SBasis) (mu : Fin n → ℤ) (hmu : Dominant mu) (I : {I : TIdx mu // StdT I}) :
    ((standardBasis hS mu hmu I : ↥(SMu mu)) : GLCoord ℤ n) = brk mu I.1 := by
  simp [standardBasis]
end Formalism.InvariantFactorPaths.ColumnFamilies
