-- Prove2me | solution 1 for Formalism.L2.Pj.Crude.crX_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:43:43.368006+00:00
-- url     : https://prove2.me/submissions/b9a236d2-7d9f-46ab-bd33-c39da125080b

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
theorem _root_.solution {R : Type} [CommRing R] {s : Set (Letter T r n)} {ℓ : Letter T r n} (h : ℓ ∈ s) :
    (X ℓ : MvPolynomial (Letter T r n) R) ∈ supported R s := by
  exact Algebra.subset_adjoin ⟨ℓ, h, rfl⟩
end Formalism.L2.Pj.Crude
