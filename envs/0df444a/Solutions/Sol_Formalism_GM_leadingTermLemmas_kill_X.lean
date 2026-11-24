-- Prove2me | solution 1 for Formalism.GM.leadingTermLemmas.kill_X
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:51:46.752475+00:00
-- url     : https://prove2.me/submissions/89a506f1-ac45-43ce-b1fb-f69f4f0e9d2f

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
variable {K σ : Type} [Field K] [Fintype σ] [DecidableEq σ]
variable (P : σ → Prop) [DecidablePred P]
namespace Formalism.GM.leadingTermLemmas
theorem _root_.solution (v : σ) : kill P (X v : MvPolynomial σ K) = if P v then 0 else X v := by
  unfold kill; rw [aeval_X]
end Formalism.GM.leadingTermLemmas
