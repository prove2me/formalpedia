-- Prove2me | solution 1 for Formalism.L2.DIV.tilde_norm_quotient
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T04:22:09.000643+00:00
-- url     : https://prove2.me/submissions/921be8bd-ba3d-4ca7-9e22-d802bd6e5b67

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_Tuples
import Definitions.Def_Formalism_LocalToGlobal_Divisibility_TuplesLemmas

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open NumberField IsDedekindDomain TensorProduct Formalism.UG Formalism.DivisionValues Formalism.EigenvalueLevelCeiling
open Formalism Formalism.L2 Formalism.L2.DIV
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {L : Type} [Field L]
namespace Formalism.L2.DIV
theorem _root_.solution (σ : E →ₐ[F] E) (ξ : Chr F E L) (h : (h90 σ).ker ≤ ξ.ker) (x : (AfE F E)ˣ) :
    tilde σ ξ ⟨h90 σ x, x, rfl⟩ = ξ x := by
  rw [tilde, dif_pos h]
  exact MonoidHom.liftOfRightInverse_comp_apply _ _ _ _ x
end Formalism.L2.DIV
