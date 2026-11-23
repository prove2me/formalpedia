-- Prove2me | solution 1 for Formalism.L2.Pj.Crude.crSig_iff
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T14:24:06.432231+00:00
-- url     : https://prove2.me/submissions/70890664-4a13-4bca-85ac-a828b1653018

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
theorem _root_.solution {τ : T} {x i : Fin (r τ)} {y : Fin n} :
    (∃ b : Fin n, (⟨τ, x, y⟩ : Letter T r n) = ⟨τ, i, b⟩) ↔ x = i := by
  constructor
  · rintro ⟨b, h⟩
    exact (Prod.mk.inj (eq_of_heq (Sigma.mk.inj h).2)).1
  · rintro rfl
    exact ⟨y, rfl⟩
end Formalism.L2.Pj.Crude
