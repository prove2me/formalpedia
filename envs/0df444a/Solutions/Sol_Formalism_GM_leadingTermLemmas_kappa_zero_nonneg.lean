-- Prove2me | solution 1 for Formalism.GM.leadingTermLemmas.kappa_zero_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:51:17.603283+00:00
-- url     : https://prove2.me/submissions/1404d8e0-c411-4b4f-a1df-7b59363578bd

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
theorem _root_.solution (o n z t r : ℕ) : 0 ≤ kap0 o n z t r := by
  unfold kap0; positivity
end Formalism.GM.leadingTermLemmas
