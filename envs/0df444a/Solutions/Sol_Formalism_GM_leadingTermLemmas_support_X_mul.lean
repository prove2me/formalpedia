-- Prove2me | solution 1 for Formalism.GM.leadingTermLemmas.support_X_mul
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:53:58.990141+00:00
-- url     : https://prove2.me/submissions/731bf842-7a0e-41b2-a69c-55797d5f3900

import Definitions.Def_Formalism_MahlerMeasure_HasOrder
import Definitions.Def_Formalism_MahlerMeasure_FinalM
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamLead

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.leadingTermLemmas
open MvPolynomial Finset Formalism.GM
variable {K σ : Type} [Field K] [Fintype σ] [DecidableEq σ] {r : ℕ} {w e : Fin r → σ}
namespace Formalism.GM.leadingTermLemmas
theorem _root_.solution (i : σ) (g : MvPolynomial σ K) :
    (X i * g).support = g.support.map (addRightEmbedding (Finsupp.single i 1)) := by
  rw [mul_comm]; exact support_mul_X i g
end Formalism.GM.leadingTermLemmas
