-- Prove2me | solution 1 for Formalism.GM.MeanGammaLemmas.initL_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:22:25.61381+00:00
-- url     : https://prove2.me/submissions/82e285b3-7363-4814-87b3-922f59442857

import Definitions.Def_Formalism_MahlerMeasure_StatementTM
import Definitions.Def_Formalism_MahlerMeasure_GamInt
import Definitions.Def_Formalism_MahlerMeasure_LegendreDigits
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_MeanGam

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM Formalism.GM.MeanGammaLemmas
open MvPolynomial Finset Formalism.GM.M
variable {p : ℕ} [hp : Fact p.Prime] {σ : Type}
namespace Formalism.GM.MeanGammaLemmas
theorem _root_.solution (v : σ) (e : ℕ) (f : MvPolynomial σ ℚ_[p]) : initL p v e f = initPart v e f := rfl
end Formalism.GM.MeanGammaLemmas
