-- Prove2me | solution 1 for Formalism.GM.leadingTermLemmas.freeze_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:34:54.347308+00:00
-- url     : https://prove2.me/submissions/7ad26648-0344-4cef-90e6-052f1be434d1

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
theorem _root_.solution (p : ℕ) [Fact p.Prime] {N r : ℕ} (LL : M.Letters N) (ρ : Fin r) (n : ℕ)
    (f : MvPolynomial (Fin N × Fin r) ℚ_[p]) : M.freeze p LL ρ n f = frz ℚ_[p] LL ρ n f := rfl
end Formalism.GM.leadingTermLemmas
