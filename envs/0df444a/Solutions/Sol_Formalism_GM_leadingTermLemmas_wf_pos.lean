-- Prove2me | solution 1 for Formalism.GM.leadingTermLemmas.wf_pos
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-25T04:00:04.821679+00:00
-- url     : https://prove2.me/submissions/1488dca6-46fa-437b-8a3c-e5627e2bd474

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
open MvPolynomial Finset
variable {σ : Type} [Fintype σ] [DecidableEq σ]
namespace Formalism.GM.leadingTermLemmas
theorem _root_.solution (m : σ →₀ ℕ) : (0 : ℝ) < wf m :=
  Finset.prod_pos (fun x _ => by exact_mod_cast Nat.factorial_pos _)
end Formalism.GM.leadingTermLemmas
