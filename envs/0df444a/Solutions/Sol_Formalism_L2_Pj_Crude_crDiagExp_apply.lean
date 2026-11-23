-- Prove2me | solution 1 for Formalism.L2.Pj.Crude.crDiagExp_apply
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:39:38.461285+00:00
-- url     : https://prove2.me/submissions/eb0498d9-122a-4631-bdd7-fd77750ee896

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
theorem _root_.solution (β : (Σ σ : T, Fin (r σ)) → Fin n) (a : T → ℕ → ℕ) (ℓ : Letter T r n) :
    diagExp r n β a ℓ = ∑ p, if crDl β p = ℓ then a p.1 p.2 else 0 := by
  simp only [diagExp, Finsupp.finset_sum_apply, Finsupp.single_apply]
  rfl
end Formalism.L2.Pj.Crude
