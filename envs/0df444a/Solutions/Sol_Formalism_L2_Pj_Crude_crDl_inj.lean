-- Prove2me | solution 1 for Formalism.L2.Pj.Crude.crDl_inj
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:14:50.786951+00:00
-- url     : https://prove2.me/submissions/357dff41-66e3-4da2-800e-2be0cf451607

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
theorem _root_.solution (β : (Σ σ : T, Fin (r σ)) → Fin n) : Function.Injective (crDl (r := r) (n := n) β) := by
  rintro ⟨σ, i⟩ ⟨τ, j⟩ h
  obtain ⟨h1, h2⟩ := Sigma.mk.inj h
  subst h1
  obtain ⟨h3, -⟩ := Prod.mk.inj (eq_of_heq h2)
  subst h3
  rfl
end Formalism.L2.Pj.Crude
