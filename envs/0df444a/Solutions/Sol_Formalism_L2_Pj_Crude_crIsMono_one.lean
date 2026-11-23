-- Prove2me | solution 1 for Formalism.L2.Pj.Crude.crIsMono_one
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:39:52.437802+00:00
-- url     : https://prove2.me/submissions/eb13bd8d-15d1-41c5-b9e5-1d6f97ae2697

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RowDeg
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CrudeMin

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
theorem _root_.solution {R : Type} [CommRing R] : crIsMono (1 : MvPolynomial (Letter T r n) R) := by
  refine ⟨0, ?_⟩
  rw [← C_1, C_apply]
end Formalism.L2.Pj.Crude
