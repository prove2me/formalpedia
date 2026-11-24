-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qb_exists_coeff
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:03:58.207631+00:00
-- url     : https://prove2.me/submissions/36e57f53-539f-4aaa-923f-aee1dbc9f3ac

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QbBasisApply
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_MemSpanStandardIffProjZero
import Theorems.Thm_Formalism_InvariantFactorPaths_ColumnFamilies_qb_basis_apply


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
theorem _root_.solution (hA : LemmaA) {M : GLMod n} (CF : ColFam M) (R : Type) [CommRing R] (x : M.ι → R) :
    ∃ a : qb_Idx CF → R, x = ∑ y, a y • qb_vecF CF R y := by
  refine ⟨fun y => (qb_basis hA CF R).repr x y, ?_⟩
  conv_lhs => rw [← (qb_basis hA CF R).sum_repr x]
  simp only [qb_basis_apply]
end Formalism.InvariantFactorPaths.ColumnFamilies
