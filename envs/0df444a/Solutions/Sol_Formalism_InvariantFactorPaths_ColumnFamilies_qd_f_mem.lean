-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.ColumnFamilies.qd_f_mem
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T12:06:57.956432+00:00
-- url     : https://prove2.me/submissions/5a412372-6161-45fd-b770-a230115f55c1

import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_TranslatesSpanCanonical
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_QbBasisApply
import Definitions.Def_Formalism_ThetaLogCoordinates_DualWeylCoordinates_DualWeylProofs_HighestVectorsRationalSpan

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
variable {n : ℕ}
variable [NeZero n]
namespace Formalism.InvariantFactorPaths.ColumnFamilies
theorem _root_.solution {M : GLMod n} (CF : ColFam M) (a : qb_Idx CF → ℚ) (j : CF.J) :
    qd_f CF a j ∈ Submodule.span ℚ (Set.range fun I : TIdx (CF.mu j) => mapCoord ℚ (brk (CF.mu j) I)) :=
  Submodule.sum_mem _ fun I _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨I.1, rfl⟩)
end Formalism.InvariantFactorPaths.ColumnFamilies
