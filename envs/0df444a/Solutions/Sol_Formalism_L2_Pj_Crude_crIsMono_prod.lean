-- Prove2me | solution 1 for Formalism.L2.Pj.Crude.crIsMono_prod
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:14:53.200133+00:00
-- url     : https://prove2.me/submissions/13c4859c-baee-496a-a14a-9193d376ca8b

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RowDeg
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CrudeMin
import Theorems.Thm_Formalism_L2_Pj_Crude_crIsMono_mul
import Theorems.Thm_Formalism_L2_Pj_Crude_crIsMono_one

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
theorem _root_.solution {R : Type} [CommRing R] {ι : Type} (s : Finset ι)
    (f : ι → MvPolynomial (Letter T r n) R) (h : ∀ i ∈ s, crIsMono (f i)) : crIsMono (∏ i ∈ s, f i) := by
  exact Finset.prod_induction f crIsMono (fun _ _ ha hb => crIsMono_mul ha hb) crIsMono_one h
end Formalism.L2.Pj.Crude
