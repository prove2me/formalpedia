-- Prove2me | solution 1 for Formalism.GM.gammaIntegralityLemmas.p_real_one_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:25:24.805062+00:00
-- url     : https://prove2.me/submissions/630fb204-b777-4eab-8fd8-c16d1a03fc9b

import Definitions.Def_Formalism_MahlerMeasure_GamInt
import Mathlib
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GamInt

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.gammaIntegralityLemmas
open Finset
variable {p : ℕ} [hp : Fact p.Prime]
namespace Formalism.GM.gammaIntegralityLemmas
theorem _root_.solution : (1 : ℝ) ≤ p := by exact_mod_cast hp.out.one_lt.le
end Formalism.GM.gammaIntegralityLemmas
