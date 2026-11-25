-- Prove2me | solution 1 for Formalism.L2.Pj.GenSect.psi_incl
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T17:09:49.059933+00:00
-- url     : https://prove2.me/submissions/49167841-bde1-4102-826c-9e8ed54f04f0

import Mathlib
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_GenSectA
import Theorems.Thm_Formalism_L2_Pj_GenSect_xv_of_not

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open Formalism Formalism.L2 Formalism.L2.Pj Formalism.L2.Pj.GenSect
open MvPolynomial
open scoped TensorProduct
variable (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω] (D m : ℕ)
variable {K Ω D m}
namespace Formalism.L2.Pj.GenSect
theorem _root_.solution (x : Fin m → Ω) (j₀ : Fin m) (f : CT Ω D j₀) : psi x j₀ (incl j₀ f) = f := by
  have h : (psi x j₀).comp (incl j₀) = AlgHom.id Ω (CT Ω D j₀) := by
    apply MvPolynomial.algHom_ext
    intro q
    simp only [AlgHom.comp_apply, AlgHom.id_apply, incl, rename_X, psi, aeval_X]
    rw [gs, if_neg q.2, xv_of_not q.2]
    try rfl
  exact DFunLike.congr_fun h f
end Formalism.L2.Pj.GenSect
