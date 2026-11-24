-- Prove2me | solution 1 for Formalism.L2.Pj.Crude.crP_rowDeg
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-24T10:46:58.027148+00:00
-- url     : https://prove2.me/submissions/a752eb5f-13f4-408c-88f8-b774a15ffe0c

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RowDeg
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CrudeMin
import Theorems.Thm_Formalism_L2_Pj_Crude_crP_isWeightedHomogeneous_crW
import Theorems.Thm_Formalism_L2_Pj_Crude_crW_weight

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.Crude
open MvPolynomial Formalism.L2.Pj
variable {T : Type} [Fintype T] [DecidableEq T] (r : T → ℕ) (n : ℕ)
variable {r n}
namespace Formalism.L2.Pj.Crude
theorem _root_.solution (k : Type) [Field k] (β : (Σ σ : T, Fin (r σ)) → Fin n) (a : T → ℕ → ℕ)
    (ha : Dom r a) : RowDeg r n k a (crP r n k β a) := by
  intro m hm σ i
  have h := crP_isWeightedHomogeneous_crW k β a ha σ i (MvPolynomial.mem_support_iff.mp hm)
  rw [crW_weight] at h
  exact h
end Formalism.L2.Pj.Crude
