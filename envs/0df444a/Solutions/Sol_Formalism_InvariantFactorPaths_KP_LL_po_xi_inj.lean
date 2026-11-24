-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.KP.LL.po_xi_inj
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:45:04.833306+00:00
-- url     : https://prove2.me/submissions/e6362810-926f-4b98-bbe3-33b6afb00edc

import Definitions.Def_Formalism_ThetaLogCoordinates_BihomogeneousPairs_LetterChainEmbeddings_LatticeEqualHolds
import Definitions.Def_Formalism_ThetaLogCoordinates_BihomogeneousPairs_LetterChainEmbeddings_PlusOp

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.KP Formalism.InvariantFactorPaths.KP.LL
open Formalism.GM
open MvPolynomial Finset Formalism.GM.M Formalism.GM.M.PhiIntegrality
variable {p : ℕ} [Fact p.Prime]
variable {N r : ℕ} [NeZero r] {D : BlockData N}
omit [NeZero r]
namespace Formalism.InvariantFactorPaths.KP.LL
theorem _root_.solution {t : ℕ} : Function.Injective (xiVar N r t) := by
  intro a b h
  simpa [xiVar] using h
end Formalism.InvariantFactorPaths.KP.LL
