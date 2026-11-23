-- Prove2me | solution 1 for Formalism.L2.Th1.A.IsDer.exists_derivation
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:21:52.741226+00:00
-- url     : https://prove2.me/submissions/7d4e716d-d2cb-4fea-ab7d-70dbbb725338

import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_StatementF
import Definitions.Def_Formalism_LocalToGlobal_TorsionIntegrality_WeierstrassTwoTorsion_WeierstrassSubstitution_FlowTrans

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
universe u
open Formalism Formalism.L2 Formalism.L2.Th1 Formalism.L2.Th1.A
variable {A : Type u} [CommRing A]
namespace Formalism.L2.Th1.A
namespace IsDer
theorem _root_.solution {D : A → A} (h : IsDer D) :
    ∃ d : Derivation ℤ A A, ∀ a, D a = d a := by
  refine ⟨Derivation.mk' (AddMonoidHom.mk' D h.1).toIntLinearMap (fun a b => ?_), fun a => rfl⟩
  simp only [AddMonoidHom.coe_toIntLinearMap, AddMonoidHom.mk'_apply, smul_eq_mul]
  exact h.2 a b
end IsDer
end Formalism.L2.Th1.A
