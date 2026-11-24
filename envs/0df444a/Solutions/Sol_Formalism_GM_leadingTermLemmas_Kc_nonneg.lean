-- Prove2me | solution 1 for Formalism.GM.leadingTermLemmas.Kc_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:26:12.064956+00:00
-- url     : https://prove2.me/submissions/261d3ade-3711-4547-b5fc-49adc39b8076

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
namespace Formalism.GM.leadingTermLemmas
theorem _root_.solution (o z : ℕ) : 0 ≤ Kc o z := Finset.sum_nonneg (fun _ _ => Nat.cast_nonneg _)
end Formalism.GM.leadingTermLemmas
