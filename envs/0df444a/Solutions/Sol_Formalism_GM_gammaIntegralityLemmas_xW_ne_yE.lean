-- Prove2me | solution 1 for Formalism.GM.gammaIntegralityLemmas.xW_ne_yE
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:51:52.941415+00:00
-- url     : https://prove2.me/submissions/7fc6db9f-d97d-4464-9542-0fc9bcd245ef

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
open MvPolynomial Finset Formalism.GM.M
variable {p : ℕ} [hp : Fact p.Prime]
variable {N r : ℕ}
namespace Formalism.GM.gammaIntegralityLemmas
theorem _root_.solution (ρ : Fin r) : xW (N := N) ρ ≠ yE ρ := by
  simp [xW, yE, Fin.castSucc_ne_last]
end Formalism.GM.gammaIntegralityLemmas
