-- Prove2me | solution 1 for Formalism.L2.Pj.Crude.crP_mem_supported
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T13:46:29.898012+00:00
-- url     : https://prove2.me/submissions/998b4668-fcc8-4d69-9b12-fb9a1fed043f

import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_RowDeg
import Definitions.Def_Formalism_LocalToGlobal_ProjectiveLattices_CrudeMin
import Theorems.Thm_Formalism_L2_Pj_Crude_crX_mem

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
theorem _root_.solution (R : Type) [CommRing R] (β : (Σ σ : T, Fin (r σ)) → Fin n) (a : T → ℕ → ℕ) :
    crP r n R β a ∈ supported R (GoodL r n β) := by
  unfold crP
  refine Subalgebra.prod_mem _ fun σ _ => Subalgebra.prod_mem _ fun kk _ => Subalgebra.pow_mem _ ?_ _
  rw [Matrix.det_apply]
  refine Subalgebra.sum_mem _ fun π _ => ?_
  rw [Units.smul_def]
  refine zsmul_mem (Subalgebra.prod_mem _ fun i _ => ?_) _
  exact crX_mem ⟨Fin.castLE kk.isLt i, rfl⟩
end Formalism.L2.Pj.Crude
