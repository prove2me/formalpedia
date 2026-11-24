-- Prove2me | solution 1 for Formalism.GM.gaussR_le_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T22:33:04.950822+00:00
-- url     : https://prove2.me/submissions/dff377ae-1f1c-4e16-a79f-54d24ea825c2

import Definitions.Def_Formalism_MahlerMeasure_StatementD
import Definitions.Def_Formalism_MahlerMeasure_MahlerMeasureProofs_GaussRad
import Theorems.Thm_Formalism_GM_gaussR_term_le

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism Formalism.GM
open Finset Polynomial
variable {K : Type} [NormedField K]
namespace Formalism.GM
theorem _root_.solution (ρ : NNReal) (P : K[X]) (c : NNReal) :
    gaussR ρ P ≤ c ↔ ∀ k, ‖P.coeff k‖₊ * ρ ^ k ≤ c := ⟨fun h k => (gaussR_term_le ρ P k).trans h, fun h => Finset.sup_le fun k _ => h k⟩
end Formalism.GM
