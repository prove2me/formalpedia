-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qb_basis_apply
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:50:13.65902+00:00
-- url     : https://prove2.me/submissions/bac32f16-461c-4c0d-a805-8bf6f4d94b12

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QbIndepField
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QbBasisApply

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
theorem _root_.solution (hA : LemmaA) {M : GLMod n} (CF : ColFam M) (R : Type) [CommRing R] (x : qb_Idx CF) :
    qb_basis hA CF R x = qb_vecF CF R x := by
  rw [qb_basis, Module.Basis.mk_apply]
end Formalism.InvariantFactorPaths.ColumnFamilies
