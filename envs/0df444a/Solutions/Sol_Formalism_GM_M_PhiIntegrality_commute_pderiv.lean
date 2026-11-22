-- Prove2me | solution 1 for Formalism.GM.M.PhiIntegrality.commute_pderiv
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T20:36:03.58049+00:00
-- url     : https://prove2.me/submissions/556e5d1a-f7d5-4e33-8010-ad0d0df72b00

import Definitions.Def_Formalism_MahlerMeasure_IsIntegral
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_PhiInt
import Theorems.Thm_P2M_Formalism_GM_M_PhiIntegrality_pderiv_comm__350abda6d36e

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.M Formalism.GM.M.PhiIntegrality
open MvPolynomial Finset
open MvPolynomial Finset
open MvPolynomial Finset
variable {p : ℕ} [hp : Fact p.Prime] {σ : Type}
namespace Formalism.GM.M.PhiIntegrality
theorem _root_.solution (i j : σ) :
    Commute (pderiv i : Derivation ℚ_[p] (MvPolynomial σ ℚ_[p]) (MvPolynomial σ ℚ_[p])).toLinearMap
      (pderiv j).toLinearMap := by
  refine LinearMap.ext fun f => ?_
  simpa using pderiv_comm' i j f
end Formalism.GM.M.PhiIntegrality
