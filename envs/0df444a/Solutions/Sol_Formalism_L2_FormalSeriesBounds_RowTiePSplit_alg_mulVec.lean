-- Prove2me | solution 1 for Formalism.L2.FormalSeriesBounds.RowTiePSplit.alg_mulVec
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-25T03:33:31.403592+00:00
-- url     : https://prove2.me/submissions/58dc0700-5d30-4616-9269-ae7d66bd9115

import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePSplitDef
import Definitions.Def_Formalism_LocalToGlobal_CharacterGerms_RowTiePSplitLA

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.L2 Formalism.L2.FormalSeriesBounds
open Formalism.L2.FormalSeriesBounds.RowTiePSplit
open Polynomial Matrix
variable {K : Type} [Field K] {n : ℕ}
namespace Formalism.L2.FormalSeriesBounds.RowTiePSplit
theorem _root_.solution (a : K) (A : Matrix (Fin n) (Fin n) K) (w : Fin n → K) :
    (algebraMap K (Matrix (Fin n) (Fin n) K) a * A) *ᵥ w = a • (A *ᵥ w) := by
  rw [← Algebra.smul_def, Matrix.smul_mulVec]
end Formalism.L2.FormalSeriesBounds.RowTiePSplit
